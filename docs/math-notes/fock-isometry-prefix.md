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

## Verified native and sector identification

Checkpoint 724e985 proves that the constructed all-operator embedding maps the
whole native family norm closure into the included norm closure. This membership
statement holds for ANY prescribed family. For an orthonormal family, the actual
restricted `prefixNativeEmbedding` equals the existing
`includedFamilyEmbedding` on the ENTIRE native closed algebra. The two genuine
star homomorphisms agree on each literal generator, hence on the polynomial
star algebra; its dense native inclusion and a closed continuous equalizer
extend the equality to the norm closure.

Checkpoint 6dec4e3 identifies Γ(V) with the actual empty-tail sector on ALL
completed tensor Fock vectors. The explicit full-source-basis word identities
follow by vacuum and creator induction. Equality of the actual bounded maps
then follows through the convergent single-word Hilbert sum, with no
finite-support restriction.

Checkpoint 6ec5ec4 proves the literal full-space intertwining identity
`isometryPrefixEmbedding V T ∘ Γ(V) = Γ(V) ∘ T` for EVERY source bounded
operator T. Coordinatewise prefix amplification acts by T in the complete
empty-tail sector, so the actual ambient compression is a left inverse on
ALL source operators. The representation sends the vacuum orbit of T to its
actual Γ(V) orbit and preserves the actual normalized ambient vacuum
expectation. These full-operator assertions require no orthonormal-family
assumption.

All three final modules were focused compiled under the shared lock with exit
0 checked before committing. Principal statements passed direct transitive
standard-axiom audits and source-integrity/diff checks. Each mathematical
checkpoint was immediately pushed successfully. The original nine prefix
representation source modules were not modified.

An implementation obstruction involved different decidable equality instances
inside square-summable singleton expressions, which could print identically
while preventing direct rewriting. A generic typed word-embedding lemma and
explicit source/target operator expressions made the intended identities
available without increasing proof resource limits.

## Remaining normal-extension boundary

Matching the native C-star embedding does not by itself establish surjectivity
on WOT-generated closures. Infinite prefix amplification is generally NOT
globally WOT continuous on unbounded nets. The proved interface is norm-ball
WOT continuity, which gives uniformly bounded convergence control.

To obtain a normal OU map on a von Neumann closure, additional bounded
approximation/closure evidence or a genuine normality framework is necessary.
No Kaplansky density, bicommutant theorem, ultraweak/predual package, WOT inverse
surjectivity, normal OU extension, or entropy theorem is assumed here.
