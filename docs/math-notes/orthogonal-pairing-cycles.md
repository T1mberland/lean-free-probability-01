# Actual alternating involution components and two half-orbits

Verified source `b734243` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalPairingCycles.lean`.
Depends on actual intrinsic partner milestone `8acafc7`; earlier sources
remain unchanged.

## Exact proven structure

For any two genuine involutive permutations `P,Q` of ANY type, put `R=P*Q`
(apply `Q` first, then `P`). The source proves

```
P(R^k(a)) = R^(-k)(P(a))                  for every integer k,
component(P,Q)(a,b) ↔ SameCycle R a b ∨ SameCycle R (P(a)) b.
```

Here component is the actual equivalence closure of moves under `P` or `Q`,
and `SameCycle R a b` means a genuine integer power of `R` takes `a` to `b`.
The component normal form needs only involutivity, even on an infinite type.
If BOTH involutions are fixed-point-free, the source additionally proves
`¬SameCycle R a (P(a))` by an actual exponent-parity argument. It follows that
the two actual half-orbits are disjoint, not merely formally different names.

Specializing to the actual intrinsic ordinary pairing partners gives
`pairingCyclePermutation p q = pairingPartner p * pairingPartner q` and:

- `pairingJoin_related_iff_two_cycles`: every raw join component is exactly
  the union of its two product half-orbits.
- `pairingCycle_not_sameCycle_partner`: the two half-orbits are distinct.
- `pairingCycle_sameCycle_partner_iff`: the genuine partner exchanges their
  sites bijectively.
- `pairingCycle_half_orbits_disjoint`: disjointness as actual sets of sites.
- `pairingCyclePermutation_self`: a doubled pairing edge gives product
  identity, hence two singleton half-orbits per two-site component.
- `pairingCycle_orbit_card_zero`: in degree zero the empty site type has no
  product orbits.

The generic public declarations are `involutionProduct_reverse_zpow`,
`involutionProduct_not_sameCycle_partner`, and
`involutionComponent_iff_two_product_orbits`.
ALL ordinary pairings, including crossings, occur. The raw join has not been
replaced by a noncrossing closure. For every existing component its two sets
are nonempty (each contains its seed), disjoint, and exhaustive. A separate
global quotient-cardinality formula, such as number of product orbits equals
twice the loop count, is not yet asserted by this module.

## Actual parity proof

Suppose `R^k(a)=P(a)`. If `k=2l`, reversing the power shows that `P` fixes
`R^l(a)`, contradicting its genuine fixed-point freedom. If `k=2l+1`, the
identity `Q=P R` and the same power reversal show that `Q` fixes `R^l(a)`.
This proves the obstruction without graph bipartiteness, supplied cycle
parity, cycle-length assumptions or finiteness premises.

For coverage, the two-orbit union is proved to be an equivalence relation
containing both actual moves. Conversely, every integer power of `R` is
shown to stay inside the generated component by genuine repeated forward
or inverse moves. Thus the equivalence closure has exactly the claimed
normal forms.

## Checks and engineering record

Focused compilation passed without warnings (3025 jobs). All nine public
theorems' transitive audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Source-integrity, staged whitespace checks and source review
passed, and the source commit was pushed immediately.

Initial repairs aligned permutation multiplication with nested function
application before combining powers. An explicit `change` retained `R` as
a product permutation after simplification had exposed `P(Q(a))`. Actual
involutivity equalities were applied at their concrete arguments rather than
assuming the function-level predicate was a simplifier rule. Integer natural
casts and the implicit point argument in `zpow_apply_comm` were made precise.
No mathematical claim was weakened or inserted as a premise.

## Remaining network frontier

The two-half-orbit structure supplies the orientation prerequisite for an
actual alternating cycle enumeration. A finite order-indexed cycle traversal,
edge-label exhaustion and correctly oriented matrix/transposed-matrix labels
must still be constructed. The genuine row/column network sum must then be
proved equal to products of ordinary cycle traces, with Euclidean operator
norm bounds and component powers. Centered leading-cycle cancellation and
random asymptotic freeness remain further separate obligations. No cycle
trace formula or random convergence theorem is claimed here.
