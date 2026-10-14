# Genuine stable orthogonal invariant-tensor spanning

Verified milestones on `feat/compact-haar-averaging`:

- `cd608f9`, `RandomMatrix/OrthogonalInvariantVanishing.lean`.
- `3f66716`, `RandomMatrix/OrthogonalInvariantSpanning.lean`.

These depend on the frozen actual normalized Haar projection, arbitrary-order
tensor representation, ordinary pairing invariance/Gram/independence, and genuine
coefficient rotation chain. Goal certification and integration are coordinator-owned.

## Exact achieved theorem

`span_pairingTensors_eq_fixedVectors r hr` proves the genuine stable-dimension
orthogonal first fundamental theorem:

The span of ALL ACTUAL intrinsic ordinary pairing tensors equals the ACTUAL
fixed-vector subspace of the degree-2r orthogonal tensor representation,
provided N = card n >= r.

Crossing pairings are permitted. Redundant site codes were quotiented by equality
of raw ordinary Setoids before defining the intrinsic pairing index. Both r = 0
and N = 0 are handled in the genuine scalar/empty-coordinate semantics.

The theorem does NOT assume invariant-tensor spanning, pairing integration,
scalar coefficient recurrences, a formal Gram inverse, traciality, or positivity
of an unrelated probability functional. Its only stable-dimension restriction
is the explicit mathematically necessary-to-this-proof N >= r. The ALL-DIMENSION
first fundamental theorem remains a distinct obligation; this is not a claim
that Goal 9 in its entirety is complete.

## Mathematical argument

`invariantTensor_coefficient_eq_zero_of_proper_splits` is the verified zero step:
actual fixedness, a fresh color, a block of size at least four, and vanishing of
all PROPER Boolean splits force the original coefficient to vanish. The two
unsplit endpoints have equal coefficients by genuine coordinate permutation
invariance; 2*(1/sqrt(2))^m < 1 for m >= 4 is proved directly.

Proper splits retain the old color and add exactly the fresh color, so the used
color count increases by one. The sum of actual color-fiber cardinalities is the
tensor degree. Reflections kill odd counts. If every used color occurs twice,
actual sigma-fiber equivalences construct a TRUE pairing site equivalence and
an injective pair-color assignment. Otherwise an even block has size at least
four and the tuple uses fewer than r colors, so stable dimension supplies a
fresh coordinate. Strong induction on r minus the used-color count proves an
invariant tensor zero if all injectively colored pair-block coefficients vanish.

Equal raw tuple kernels admit two injective color maps from their common finite
quotient. Extending these to a genuine coordinate permutation proves actual
invariant coefficients depend only on their equality pattern. Choose one fixed
injective pair-color assignment; subtract the finite combination of ACTUAL
pairing tensors with coefficients equal to these actual colored evaluations.
The verified isolating-coordinate property and equality-pattern invariance
annihilate ALL pair-block coefficients of the residual. The zero-evaluation
induction proves that residual is zero, yielding the actual span theorem.

## Verification and next obligations

Both modules compile warning free under the common lock. Principal theorems passed
transitive standard-logic audits; the literal stable FFT statement was inspected.
Integrity guard and staged diff checks passed before atomic commits, all immediately
pushed. Minor failures concerned reserved variable spelling, finite-set cardinality
lemma casing, and unused automatically included assumptions; no mathematical
statement was weakened.

The genuine stable Gram inverse is already proved. Next combine that inverse,
actual invariant span, and actual Haar projection to derive the TRUE arbitrary
matrix-entry Weingarten pairing formula in stable dimension. Low-dimensional
spanning/pseudoinverse treatment remains separate. General joint asymptotic
freeness still needs actual estimates and convergence-mode arguments; expected
traces alone do not imply probability, almost-sure or strong convergence.
