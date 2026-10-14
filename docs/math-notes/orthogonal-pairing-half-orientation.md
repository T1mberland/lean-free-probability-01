# Actual chosen half-orbits and deterministic-edge orientation

Verified milestone `1c15463` on `feat/orthogonal-trace-words`:
`FreeProbability/RandomMatrix/OrthogonalPairingHalfOrientation.lean`.
Depends on actual two-half-orbit and quotient component results. All older
sources remain unchanged.

## Genuine selection and proved structure

For intrinsic ordinary pairings `p,q`, let `R=pairingPartner p * pairingPartner q`.
For a site `a`, the raw component quotient supplies an actual representative
`c.out`. Define `pairingHalf p q a` to mean that `a` is in the genuine `R`
orbit of this representative. Thus one ACTUAL product half-orbit is selected
in each raw component; neither a bipartition nor an orientation witness is
supplied as a premise.

The source proves:

- `pairingHalf_rotate_iff`: actual `R` preserves the chosen half.
- `pairingHalf_iff_cycle_of_component`: membership is exactly the genuine
  selected orbit of the specified component.
- `pairingHalf_component_seed`: each representative belongs to its half.
- `pairingHalf_partner_iff`: first actual partner exchanges half/complement.
- `pairingHalf_second_partner_iff`: second actual partner does the same.

`PairingHalfSites` is the actual selected subtype, and
`pairingHalfPermutation` restricts the genuine `R` to a real permutation of
that subtype; its application is recorded by `pairingHalfPermutation_apply`.
Every first or second pairing edge consequently meets the half exactly once.

## Actual edge labels and orientation bits

For ANY deterministic-edge code `e : Fin(2*r) ≃ Fin r × Fin 2`, take
`q=Quotient.mk e`. Its endpoints are literally `e.symm(k,0)` and
`e.symm(k,1)`. `pairingEdgeOrientation` is false if endpoint zero lies in the
half and true otherwise. `pairingSelectedEndpoint` constructs the actual
selected subtype element, with its membership proved from the complement
exchange when endpoint one must be selected.

`pairingEdgeHalfEquiv p e : Fin r ≃ PairingHalfSites p (Quotient.mk e)` proves
true exhaustion: one selected endpoint per deterministic label, and every
selected site occurs. The inverse recovers the actual code first coordinate
(`pairingEdgeHalfEquiv_symm_apply`).
`pairingSelectedEndpoint_coordinate` proves that the second coordinate is
exactly the actual orientation bit, interpreted as endpoint zero or one.
Finally `pairingHalfSites_card` proves the selected half has cardinality `r`.

ALL ordinary pairings, crossing included, are allowed. Degree zero is
included with empty selected subtype and empty label equivalence. Doubled
edges are handled by the actual half-orbit selection already proved; there
is no nontrivial-cycle assumption. The chosen representatives need not be
canonical, but the definition fixes actual choices and all properties are
proved for those choices.

## Proof and verification

Equality of raw quotient classes under both partner moves and the actual
product lets membership use a common component representative. The previously
proved two-orbit coverage and disjointness then show the first partner
exchanges the halves. The identity `Q=P R` and `R` invariance give the second
partner result. Actual endpoint swap under the supplied code proves the
orientation membership, and code first coordinates prove injection and
surjection of the edge-label equivalence.

Focused compilation passed without warnings (3027 jobs). All fifteen public
definitions/theorems audited have only `propext`, `Classical.choice`, and
`Quot.sound`. Source integrity, staged whitespace checks and source review
passed; the source commit was pushed immediately. One proof adjustment
avoided an extra reflexivity tactic after an iff rewrite had already closed
the representative-membership goal. No mathematical statement was changed.

## Remaining original paired-network transfer

This closes the genuine factor-exhaustion/orientation prerequisite. The next
step must identify paired colorings with arbitrary colorings of the selected
half, prove that each deterministic edge entry is the corresponding matrix
or transpose entry under the actual orientation, and show the paired finite
network equals the actual permutation network of `pairingHalfPermutation`
with these oriented matrices. The selected permutation's orbit quotient
must also be identified with the raw component quotient to give exactly
one dimension factor per raw loop.

The generic actual cycle-trace and Euclidean operator-norm theorems are
available, but their application to these original paired networks is not
yet claimed. Singleton centered cancellation, combined component counts,
actual expected trace decay, multiple traces, independent Haar colors and
random convergence modes remain separate dependent obligations.
