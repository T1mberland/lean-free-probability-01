# Arbitrary-isometry prefix representation and native identification

## Verified representation before native identification

The original prefix/tail construction is a genuine complete Hilbert-space
representation: exact ordered word decomposition, orthogonal complete prefix
sectors, actual all-bounded-operator amplification, exact creators and adjoints,
and WOT continuity on each actual source operator norm ball. Its first five
source checkpoints are 52adc8f, 207a4cd, 900a295, abbecf3, and 539ffb2.
Their exact initial sum-alphabet scope is recorded in fock-prefix-tail.md.

The following four additional sources complete the representation for ANY
one-particle Hilbert isometry V : H →ₗᵢ[ℂ] K between complete complex Hilbert
spaces, on the independently fixed literal completed tensor Fock spaces:

- 95aef69: a genuine onto word Hilbert unitary for any alphabet equivalence,
  with literal List.map action on word vectors.
- 12e2990: extend the image of a full source basis to a full target basis;
  split target indices into the included range and its complement; construct
  the actual whole-space unitary and unital injective bounded-operator
  embedding isometryPrefixEmbedding V between fixed tensor Fock spaces.
- 621c0ab: the embedding sends tensorCreation H h exactly to
  tensorCreation K (V h), and likewise its actual Hilbert adjoint, for EVERY
  h. The basis identities extend by continuous complex-linear creator maps
  and genuinely convergent full Hilbert-basis expansions.
- f3f48e4: that actual arbitrary-isometry tensor embedding is WOT continuous
  on each source operator norm ball. Exact included real-field action holds
  for any prescribed family, without requiring orthonormality for this action.

No countability, spanning-family, or nontriviality assumption is added. Each
final source module was focused compiled successfully under the shared lock;
principal declarations were transitively audited with only propext,
Classical.choice, and Quot.sound. Source-integrity and diff checks passed.
Each atomic mathematical commit was pushed successfully immediately.

A direct nested composition in the bounded-WOT transport theorem exceeded
Lean's deterministic elaboration limit. Naming the generic transported map
and providing separately typed continuity proofs for its three factors solved
that elaboration problem, without changing resource limits or mathematics.

## Next native and sector identification milestones

The next proof identifies the constructed all-operator embedding on a native
orthonormal-family norm closure with the existing includedFamilyEmbedding.
The actual all-vector field identities and continuous star-algebra maps should
first show membership in the included norm closure, then equality on the dense
polynomial star algebra and hence the native closure.

The empty-tail sector should be identified with the actual second-quantized
isometry Γ(V), using vacuum and full source basis words. This must yield the
literal full-space identity Φ(V)(T) Γ(V) = Γ(V) T for ALL source bounded T,
not merely polynomial operators. It will establish the actual fullcompression
left inverse and vacuum preservation of the representation.

These are current proof targets, not achievements asserted in this note.
Further verified checkpoints will update the project ledger through the
coordinator.

## Remaining normal-extension boundary

Matching the native C-star embedding does not by itself establish surjectivity
on WOT-generated closures. Infinite prefix amplification is generally NOT
globally WOT continuous on unbounded nets. The proved interface is norm-ball
WOT continuity, which gives uniformly bounded convergence control.

To obtain a normal OU map on a von Neumann closure, additional bounded
approximation/closure evidence or a genuine normality framework is necessary.
No Kaplansky density, bicommutant theorem, ultraweak/predual package, WOT inverse
surjectivity, normal OU extension, or entropy theorem is assumed here.
