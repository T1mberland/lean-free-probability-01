# Actual OU range in literal prescribed-family double commutants

## Literal range theorem

For ANY prescribed e : I → H in a complete complex Hilbert space, define its
literal field double commutant by the set

Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))).

No identification with a WOT-generated or norm-generated closure is used.
No orthonormality, spanning, countability, or nontriviality assumption is needed
for the range result.

The genuine all-operator prefix representation sends a source double-commutant
operator into the included field double commutant. Actual second-quantized
unitary conjugation transports that membership into the rotated field double
commutant.

Every B in the ORIGINAL prescribed-family commutant has an actual suffix image
commuting with each rotated field. The exact arbitrary-vector source-field
commutator defect proves commutation with the included field. The geometric
orthogonal-complement creator and annihilator commutation proves commutation
with the second-coordinate noise field. The actual rotation is the REAL linear
combination of these fields, with the conjugate-scalar adjoint treated exactly.

Consequently an operator in the rotated field double commutant commutes with
suffix(B). The actual Γ inclusion and its adjoint intertwine all suffix images.
Thus its actual Γ-first compression commutes with EVERY B in the original
family commutant and belongs to the original literal double commutant.

## Actual maps and stronger verified interfaces

`ouDoubleCommutantRaw r s hrs` is literally actual first-coordinate prefix
embedding followed by actual second-quantized doubled rotation and actual
first-coordinate Γ-compression. It acts on ALL source bounded operators. Its
prescribed-family double-commutant range is proved, not assumed.

`ouDoubleCommutantRawCP` bundles the SAME operator formula as a completely
positive map at EVERY canonical finite matrix level. The input matrix first
passes through a genuine CStarMatrix star homomorphism, preserving its full
positive cone, then through the previously verified actual rotated compression
CP map. No scalar Gram-only substitute or cone reflection assumption enters.
The actual map is unital, operator-norm contractive, and preserves the actual
normalized ambient vacuum expectation.

`ouDoubleCommutantTimeCP t ht` uses the genuine parameters exp(-t) and
sqrt(1-exp(-2t)) for t≥0, preserving those interfaces and literal range.
Time zero fixes EVERY source bounded operator, from actual rotation(1,0)=id,
second quantization of id, and the literal all-operator prefix-compression left
inverse. This zero-time statement does not rely on Wick polynomial norm
density in all B(Fock).

Both maps are genuinely WOT continuous on EVERY source operator norm ball.
The proof composes actual prefix norm-ball WOT continuity, actual unitary WOT
conjugation, and actual WOT Γ-compression. Infinite amplification is not claimed
globally WOT continuous on arbitrary unbounded nets.

## Verified source checkpoints

- b4dd72f, OrnsteinUhlenbeckVonNeumannRangeCompression.lean: actual Γ-adjoint
  suffix intertwining and commutation transfer through ambient compression.
- 7581407, OrnsteinUhlenbeckVonNeumannRangeFields.lean: actual real-field rotation
  decomposition and original prescribed-family suffix commutation with rotated
  fields.
- 5a02bb5, OrnsteinUhlenbeckVonNeumannRange.lean: generic unitary double-commutant
  transport, literal rotated compression range, and actual raw OU map range.
- 5eedcad, OrnsteinUhlenbeckVonNeumannRangeCP.lean: full all-matrix CP bundle,
  unit, norm contraction, actual vacuum preservation and literal range.
- 62afeb7, OrnsteinUhlenbeckVonNeumannRangeTime.lean: genuine nonnegative-time CP
  maps, inherited interfaces, and all-operator zero-time identity.
- 5143895, OrnsteinUhlenbeckVonNeumannRangeWOT.lean: actual prefix norm-ball map
  and all-operator OU norm-ball WOT continuity.

Each final focused build was serialized under the common lock and its exit 0
was explicitly checked before committing. Principal statements passed direct
transitive axioms audits with only propext, Classical.choice, and Quot.sound.
The proof-source integrity guard and diff checks passed. Every meaningful
atomic commit was immediately pushed successfully. The pinned dependencies
and all previous frozen proof modules/notes were untouched.

## Implementation discoveries

A direct concrete doubled-space unitary membership proof caused excessive
unfolding of full Hilbert basis choice and operator definitions. The diagnostic
showed more than 120,000 attempted Classical.choice reductions. A generic
unitary image theorem and local irreducibility of the large basis/field/embedding
constructions solved this elaboration issue without increasing resource limits.
The kernel still checks the exact original definitions.

The image expression must retain the SAME bundled toMulEquiv coercion used by
the generic double-centralizer theorem. An explicitly typed image equality
avoids relying on elaborator rewriting between different equivalence metadata.
Time parameters carry dependent unit-circle proofs, so simp's dependent
congruence is used for zero-time specialization rather than an ill-typed direct
rewrite of the real parameters while retaining the old proof.

## Remaining Goal 10 obligations

The coordinator's planned tensorFamilyVonNeumannAlgebra has the exact carrier
used here. Restricting the CP map to that genuine norm-closed C-star carrier,
with all intrinsic finite-matrix cone checks, will use its verified subtype
interfaces. Faithfulness/traciality are being developed independently by the
coordinator and are not assumptions in the range theorem.

Additive semigroup laws on ALL bounded operators, or on the entire literal
double-commutant carrier, have not been proved by this checkpoint. The existing
native C-star semigroup laws cover a different previously verified scope.
Positive-supremum normality, an appropriate normal-map interface, full normal
von Neumann OU semigroup, L1 extension, hypercontractivity, logarithmic Sobolev,
and entropy conclusions remain separate mathematical obligations.
