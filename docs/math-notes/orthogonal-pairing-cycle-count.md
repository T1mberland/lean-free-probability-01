# Actual product-orbit count and two-element component fibers

Verified source milestone `fd93855` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalPairingCycleCount.lean`.
Depends on the actual two-half-orbit theorem `b734243`; older files are unchanged.

## Proven interfaces

`PairingProductOrbits p q` is the quotient of the actual site type by
`SameCycle` of the genuine product permutation. It includes fixed singleton
orbits. `PairingJoinComponents p q` is the quotient by the ORDINARY raw join.
The actual quotient map `pairingCycleComponentMap` sends each product orbit
to its raw join component, with well-definedness supplied by the proved
component decomposition.

Public results in `FreeProbability.Orthogonal`:

- `pairingCycleComponentMap_surjective`: actual surjectivity.
- `pairingCycleComponentMap_fiber_iff`: the fiber over a component `c` consists
  exactly of the product classes of `c.out` and `pairingPartner p c.out`.
- `pairingCycleComponentMap_fiber_card`: EVERY actual fiber has cardinality two.
- `pairingCycle_orbit_card_eq_twice_loopCount`: the exact global count

```
card(PairingProductOrbits p q) = 2 pairingLoopCount p q.
```

There is no counting or cycle formula premise. All ordinary crossing pairings
are included, and the join has not been replaced by a noncrossing closure.
Degree zero is included: the source and target quotient types are empty, the
fiber assertion is vacuous, and the global count is zero. Doubled edges are
also included: product identity yields two singleton orbits per raw two-site
component. Using only a nontrivial-cycle factorization would incorrectly
omit these singleton orbits; the actual `SameCycle` quotient avoids that.

## Proof and verification

The two raw component half-orbits proved earlier give the exact fiber
characterization. Their proved parity-based separation makes the two
quotient classes distinct. The actual fiber is counted as a two-element
finite set, and `Equiv.sigmaFiberEquiv` decomposes the whole source into its
actual fibers. Summing the exact fiber cardinality proves the global count.

Focused compilation passed without warnings (3026 jobs). All four public
theorems' transitive audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Source integrity, staged whitespace checks and source review
passed, and the source commit was pushed immediately. The only initial
repair was explicitly commuting the final natural multiplication from
`card(components)*2` to `2*loopCount`; no mathematical statement changed.

## Remaining cycle-trace frontier

The quotient/fiber API now supplies both the exact component count and
orientation pairing. The next step must enumerate each actual finite product
orbit by `Fin(card orbit)` with a genuinely closing cyclic traversal,
including singleton orbits. A chosen half-orbit in each raw component must
then orient deterministic edges and exhaust each matrix label exactly once.
Only after proving the actual network finite sum equals products of cycle
traces can Euclidean operator-norm bounds and distance-controlled contraction
powers be claimed. Centered cancellation, independent Haar colors and random
convergence modes remain later distinct obligations.
