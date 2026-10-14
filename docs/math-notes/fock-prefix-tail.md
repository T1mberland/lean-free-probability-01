# Actual prefix/tail amplification and bounded-WOT scope

## Verified sum-alphabet representation

For arbitrary types I and J, every word over Sum I J has a UNIQUE ordered
initial List I prefix and an empty tail or a tail starting with an outside
J letter. The literal tail type is Option (J × List (Sum I J)).
`prefixTailEquiv` splits at the first outside letter and its inverse concatenates
the included prefix and the tail. No reordering or commutation occurs.

Each fixed tail gives an isometric copy of the COMPLETE WordSpace I inside
WordSpace (Sum I J). Distinct tails are orthogonal. The sum of these closed
copies is total because every word has this decomposition. The actual unitary
`prefixTailDecomposition` therefore identifies the whole completed word space
with the external lp-2 Hilbert sum of all prefix copies, including arbitrary
infinite amplitudes.

For ANY complete complex Hilbert E and arbitrary index A,
`hilbertAmplification` applies the same actual bounded operator T coordinatewise
on the entire lp-2 Hilbert sum. Membership follows from the operator norm bound;
the output norm is at most ‖T‖ times the input norm. Inner products as convergent
coordinate sums establish adjoint preservation. `hilbertAmplificationHom` is a
true unital star homomorphism on ALL B(E), not merely polynomial operators.
It is injective when A is nonempty.

Conjugation through the actual prefix/tail unitary gives the true unital
injective `prefixOperatorEmbedding` on all B(WordSpace I). Its action on every
complete tail sector is exactly T. Included-letter creation, its adjoint
annihilation, and the real field are transported literally to the operators
indexed by Sum.inl i. Finite-word identification was extended through genuine
complete-sector density, not assumed for infinite amplitudes.

## Correct continuity scope

`hilbertAmplification_boundedWOT_continuous` proves actual weak-operator
continuity on EVERY source norm ball {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ C}.
The same theorem holds for `prefixOperatorEmbedding` by actual unitary
conjugation. The ball has the induced genuine WOT topology.

For a fixed output vector y, finite-coordinate input vectors give continuous
WOT coefficient orbits. They form a dense linear submodule of the complete
Hilbert sum. The uniform Lipschitz bound ‖y‖ C extends joint input/coefficient
continuity to all infinite input amplitudes. Thus the theorem controls all
matrix coefficients, including infinite-coordinate test vectors.

Infinite amplification is generally NOT globally WOT continuous on unbounded
nets. No such theorem or assumption is used. A future normality interface must
use uniformly bounded WOT convergence, ultraweak continuity, or preservation of
bounded increasing positive suprema.

## Published checkpoints and verification

- 52adc8f: exact ordered word bijection and inverse proofs.
- 207a4cd: orthogonal complete tail copies, totality, full Hilbert-sum unitary.
- 900a295: actual bounded unital star-homomorphic Hilbert amplification.
- abbecf3: faithful prefix embedding and exact creator/annihilator/field action.
- 539ffb2: genuine WOT continuity restricted to each source operator norm ball.

These five mathematical modules are frozen. Each final focused build completed
with exit 0 before its commit, direct transitive audits used only the standard
three Lean axioms, and source-integrity/diff checks passed. Each atomic commit
was immediately pushed successfully. No pinned dependency revision changed.

A subsequent independent helper, 95aef69, constructs `wordAlphabetUnitary` for
an arbitrary alphabet equivalence using a genuinely total orthonormal word
basis. Its word action is literal List.map, and its complete Hilbert unitary
statement was focused compiled and audited. It is intended for the arbitrary
isometry bridge below.

## Remaining arbitrary-isometry and normal-extension obligations

The verified operator embedding is currently the sum-alphabet word
representation. Transport to the independently fixed literal tensor Fock spaces
for EVERY one-particle isometry V : H →ₗᵢ[ℂ] K remains to be implemented. A
prospective construction extends V applied to a full basis of H to a full
basis of K, splits its indices into the included range and its complement,
then transports the above representation through actual word-alphabet and
completed-tensor unitaries. Exact creator identification for every h, not only
selected basis vectors, must be proved by continuity and basis density.

Only after that bridge can it be compared with the existing native included
algebra embedding and used for its bounded-WOT continuity or closure image.
Surjectivity of included WOT compression and a normal OU self-map on a von
Neumann closure are not conclusions of this checkpoint. Kaplansky density,
bicommutant, and ultraweak/predual machinery remain explicit further
mathematical dependencies; no entropy or hypercontractivity claim follows.
