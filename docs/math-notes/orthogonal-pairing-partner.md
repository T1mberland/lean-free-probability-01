# Actual intrinsic ordinary pairing partners and join components

Verified source milestone `8acafc7` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalPairingPartner.lean`.
All earlier sources remain unchanged.

## Exact proved interfaces

For a site code `e : Fin(2*r) ≃ Fin r × Fin 2`, `codePairingPartner e`
is the actual permutation conjugating the exchange of `0,1` in the second
coordinate. It exchanges the two sites in each pair. The source proves its
involutivity, absence of fixed points, and raw relation with the original
site. The actual pairing relation is exactly

```
pairingSetoid e a b ↔ b=a ∨ b=codePairingPartner e a.
```

The unique distinct related endpoint proves
`codePairingPartner_eq_of_setoid_eq`: the permutation is unchanged by pair
renumbering or orientation changes. The intrinsic `pairingPartner p`
is defined using `p.out`, and `pairingPartner_mk` proves that ANY code gives
the same actual permutation. Thus the quotient representation is not an
extra choice-dependent assumption.

Further intrinsic statements are
`pairingPartner_involutive`, `pairingPartner_ne_self`,
`pairingPartner_related`, `pairingSetoid_iff_eq_or_partner` and
`pairingPartner_eq_iff`. The last result says that the actual partner
permutation determines the intrinsic pairing completely.

For two intrinsic pairings, `pairingMoves p q a b` means that either actual
partner takes `a` to `b`. Its symmetry follows from the proved involutions.

- `pairingJoin_eq_partner_moves` proves that the ORDINARY raw Setoid join is
  precisely `Relation.EqvGen.setoid` of these two genuine moves.
- `pairingJoin_related_iff_reachable` proves that two sites are in the same
  raw join class exactly when they are reachable through finitely many
  partner moves (`Relation.ReflTransGen`).
- `pairingLoopCount_eq_partner_components` identifies the existing genuine
  quotient loop count with the number of these actual move components.

ALL ordinary pairings, including crossing pairings, are included. There is
no noncrossing closure, distinct-code assumption or supplied orbit relation.
Half-degree zero is allowed: partner statements with an endpoint are
vacuous on its empty site type and the component quotient is empty.

## Proof and verification

The code-level permutation is obtained directly from an actual site
equivalence and the actual swap permutation. Equality of first coordinates
and the two-element second coordinate give the raw relation characterization.
Its uniqueness gives representation independence. The raw supremum universal
property yields equality with the generated move relation. Since every move
is reversible by its genuine involution, equivalence closure equals actual
reflexive transitive reachability.

Focused compilation passed without warnings (3024 jobs). All fifteen public
theorems' transitive audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Source integrity, staged whitespace checks and source review
passed, and the source commit was pushed immediately.

Initial engineering repairs exposed product-coordinate eta before cancelling
an equivalence, gave `Prod.ext` both coordinates explicitly, and unfolded the
actual kernel relation when transporting the quotient representative. The
reachability conversion is located in the pinned `Relation.EqvGen` namespace,
not directly under `Relation`. Deprecated symmetry notation was replaced by
`Std.Symm`. No intended mathematical statement was changed or assumed.

## Remaining cycle frontier

This is the genuine involution/component prerequisite for network cycles.
It does not yet decompose a deterministic network into cycle traces. The
next step must construct the actual alternating cycles of the pairing
involution and the deterministic-edge pairing, with a consistent orientation,
ordered matrix labels and transposes, and prove that the cycle components
exhaust the sites. Then the actual network finite sum must be shown equal
to the corresponding product of ordinary traces, before claiming Euclidean
operator-norm bounds. Sharp Weingarten-distance estimates are available, but
centered trace cancellation and random asymptotic freeness remain separate.
